import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5852 = true := by
  decide +kernel

theorem tot5852 : totK PD2M8K2 D2M8K2.t5852 = [0, 98349951476, 356491802970, 329806808175, 76179041852, 3552795014, 0, 0] := by
  decide +kernel

theorem rows5853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5853 = true := by
  decide +kernel

theorem tot5853 : totK PD2M8K2 D2M8K2.t5853 = [0, 171134767204, 453975737145, 260826897780, 25478622528, 0, 0, 0] := by
  decide +kernel

theorem rows5854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5854 = true := by
  decide +kernel

theorem tot5854 : totK PD2M8K2 D2M8K2.t5854 = [48929220385, 210785593079, 405885071245, 225791389469, 17297076766, 0, 0, 0] := by
  decide +kernel

theorem rows5855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5855 = true := by
  decide +kernel

theorem tot5855 : totK PD2M8K2 D2M8K2.t5855 = [176926516189, 451475581047, 268883870118, 29073430889, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
