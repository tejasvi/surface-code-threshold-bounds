import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1088 = true := by
  decide +kernel

theorem tot1088 : totK PA10K2 A10K2.t1088 = [0, 136007313416, 1094680372096, 2111513283052, 1333120397807, 267541864431, 17754888877, 0, 0, 0] := by
  decide +kernel

theorem rows1089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1089 = true := by
  decide +kernel

theorem tot1089 : totK PA10K2 A10K2.t1089 = [0, 281204290441, 1144263229671, 1864913265484, 1328908337828, 246540780390, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1090 = true := by
  decide +kernel

theorem tot1090 : totK PA10K2 A10K2.t1090 = [0, 457582990582, 1734219314528, 1995954369341, 646264838704, 42288144847, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1091 = true := by
  decide +kernel

theorem tot1091 : totK PA10K2 A10K2.t1091 = [0, 154507806975, 1113768610867, 2173057434899, 1361936197686, 237811253561, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
