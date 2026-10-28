import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4080 = true := by
  decide +kernel

theorem tot4080 : totK PD2M8K2 D2M8K2.t4080 = [0, 0, 162186973847, 459034452959, 275979571149, 29200286642, 0, 0] := by
  decide +kernel

theorem rows4081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4081 = true := by
  decide +kernel

theorem tot4081 : totK PD2M8K2 D2M8K2.t4081 = [0, 0, 174130972696, 479178757456, 236881058667, 10404426584, 0, 0] := by
  decide +kernel

theorem rows4082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4082 = true := by
  decide +kernel

theorem tot4082 : totK PD2M8K2 D2M8K2.t4082 = [0, 0, 170887433374, 465597260973, 249418166411, 20949581993, 0, 0] := by
  decide +kernel

theorem rows4083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4083 = true := by
  decide +kernel

theorem tot4083 : totK PD2M8K2 D2M8K2.t4083 = [0, 0, 187086945771, 463266862671, 231271860984, 15111117465, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
