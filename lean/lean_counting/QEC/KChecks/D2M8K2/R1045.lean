import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4180 = true := by
  decide +kernel

theorem tot4180 : totK PD2M8K2 D2M8K2.t4180 = [0, 0, 203053810222, 469718228449, 211914357717, 13912096232, 0, 0] := by
  decide +kernel

theorem rows4181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4181 = true := by
  decide +kernel

theorem tot4181 : totK PD2M8K2 D2M8K2.t4181 = [0, 0, 120117221845, 441166940117, 312159502616, 22593098950, 0, 0] := by
  decide +kernel

theorem rows4182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4182 = true := by
  decide +kernel

theorem tot4182 : totK PD2M8K2 D2M8K2.t4182 = [0, 0, 81455151788, 371227579442, 419647284625, 40985452751, 0, 0] := by
  decide +kernel

theorem rows4183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4183 = true := by
  decide +kernel

theorem tot4183 : totK PD2M8K2 D2M8K2.t4183 = [0, 0, 163398863658, 444927919813, 278383656559, 28278694298, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
