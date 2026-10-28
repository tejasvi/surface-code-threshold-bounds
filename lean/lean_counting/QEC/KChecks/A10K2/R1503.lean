import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6012 = true := by
  decide +kernel

theorem tot6012 : totK PA10K2 A10K2.t6012 = [0, 297964372051, 1188225354253, 1911716112647, 1337636169685, 249886199628, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6013 = true := by
  decide +kernel

theorem tot6013 : totK PA10K2 A10K2.t6013 = [0, 465823610262, 1743372007655, 1976274514187, 567812133993, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6014 = true := by
  decide +kernel

theorem tot6014 : totK PA10K2 A10K2.t6014 = [0, 0, 773427081926, 2102357262420, 1486125243473, 310119863354, 24614390653, 0, 0, 0] := by
  decide +kernel

theorem rows6015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6015 = true := by
  decide +kernel

theorem tot6015 : totK PA10K2 A10K2.t6015 = [0, 279438172082, 1217863475819, 1973332820870, 1147845779620, 171443875026, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
