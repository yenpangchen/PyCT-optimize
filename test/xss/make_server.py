from xmlrpc.server import DocXMLRPCServer

#######################################################################################
# Remember to modify the source code of line 898 in /usr/lib/python3.8/xmlrpc/server.py
# from: return documenter.page(html.escape(self.server_title), documentation)
#   to: return documenter.page(self.server_title, documentation)
# in order to make this example work!
#######################################################################################

def make_server(title):
    serv = DocXMLRPCServer(("localhost", 8080), logRequests=False)
    serv.set_server_title(title) #"DocXMLRPCServer Test Documentation")
    serv.set_server_name("DocXMLRPCServer Test Docs")
    serv.set_server_documentation("This is an XML-RPC server's documentation")
    generated = serv.generate_html_documentation()
    return '<script>' in generated
