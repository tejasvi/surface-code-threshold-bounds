import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9852 = true := by
  decide +kernel

theorem tot9852 : totK PD2M8K2 D2M8K2.t9852 = [0, 0, 208221063721, 461378046912, 202015697617, 12096313584, 0, 0] := by
  decide +kernel

theorem rows9853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9853 = true := by
  decide +kernel

theorem tot9853 : totK PD2M8K2 D2M8K2.t9853 = [0, 0, 19168591844, 357515298982, 412437540582, 61050597899, 1053411165, 0] := by
  decide +kernel

theorem rows9854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9854 = true := by
  decide +kernel

theorem tot9854 : totK PD2M8K2 D2M8K2.t9854 = [0, 0, 85071533861, 313842531833, 366167479182, 91710563855, 3667207281, 0] := by
  decide +kernel

theorem rows9855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9855 = true := by
  decide +kernel

theorem tot9855 : totK PD2M8K2 D2M8K2.t9855 = [0, 0, 154226912705, 459680021200, 268566814242, 16861484491, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
