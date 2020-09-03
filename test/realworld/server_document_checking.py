from xmlrpc.server import DocXMLRPCServer

#######################################################################################
# Remember to modify the source code of line 898 in /usr/lib/python3.8/xmlrpc/server.py
# from: return documenter.page(html.escape(self.server_title), documentation)
#   to: return documenter.page(self.server_title, documentation)
# in order to make this example work!
#######################################################################################

def server_document_checking(title, name, documentation):
    serv = DocXMLRPCServer(("localhost", 8080), logRequests=False)
    serv.set_server_title(title) #"DocXMLRPCServer Test Documentation")
    serv.set_server_name(name) #"DocXMLRPCServer Test Docs")
    serv.set_server_documentation(documentation) #"This is an XML-RPC server's documentation")
    serv.register_introspection_functions()
    serv.register_multicall_functions()
    serv.register_function(lambda x, y: x + y)
    serv.register_instance(DocXMLRPCServer(("localhost", 8081)))
    generated = serv.generate_html_documentation()
    if '<script>' in generated:
        return 'dangerous'
    else:
        return 'safe'
