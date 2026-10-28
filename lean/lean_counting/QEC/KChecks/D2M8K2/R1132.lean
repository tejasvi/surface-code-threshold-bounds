import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4528 = true := by
  decide +kernel

theorem tot4528 : totK PD2M8K2 D2M8K2.t4528 = [0, 0, 183957131057, 460348256843, 229210997454, 17654959963, 0, 0] := by
  decide +kernel

theorem rows4529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4529 = true := by
  decide +kernel

theorem tot4529 : totK PD2M8K2 D2M8K2.t4529 = [0, 0, 63924636563, 347437879222, 404400603006, 69407987919, 1075657031, 0] := by
  decide +kernel

theorem rows4530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4530 = true := by
  decide +kernel

theorem tot4530 : totK PD2M8K2 D2M8K2.t4530 = [0, 0, 21280121782, 283813434911, 455623833013, 110347282434, 3804183361, 0] := by
  decide +kernel

theorem rows4531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4531 = true := by
  decide +kernel

theorem tot4531 : totK PD2M8K2 D2M8K2.t4531 = [0, 0, 200580975726, 469979537746, 233795060913, 20855590267, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
