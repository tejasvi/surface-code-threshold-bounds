import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5684 = true := by
  decide +kernel

theorem tot5684 : totK PD2M8K2 D2M8K2.t5684 = [0, 0, 200423820489, 458212915907, 173048365266, 11894306413, 0, 0] := by
  decide +kernel

theorem rows5685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5685 = true := by
  decide +kernel

theorem tot5685 : totK PD2M8K2 D2M8K2.t5685 = [0, 170657820507, 437458433112, 264482749873, 24514161455, 0, 0, 0] := by
  decide +kernel

theorem rows5686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5686 = true := by
  decide +kernel

theorem tot5686 : totK PD2M8K2 D2M8K2.t5686 = [0, 179744015508, 448033297651, 231593535746, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows5687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5687 = true := by
  decide +kernel

theorem tot5687 : totK PD2M8K2 D2M8K2.t5687 = [0, 61608472202, 346636716191, 404773774774, 67547304310, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
