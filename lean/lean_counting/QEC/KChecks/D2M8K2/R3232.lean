import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12928 = true := by
  decide +kernel

theorem tot12928 : totK PD2M8K2 D2M8K2.t12928 = [0, 0, 215083066874, 488648242974, 176028633196, 9849381256, 0, 0] := by
  decide +kernel

theorem rows12929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12929 = true := by
  decide +kernel

theorem tot12929 : totK PD2M8K2 D2M8K2.t12929 = [0, 156964551489, 439551427271, 295087157719, 33055647836, 0, 0, 0] := by
  decide +kernel

theorem rows12930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12930 = true := by
  decide +kernel

theorem tot12930 : totK PD2M8K2 D2M8K2.t12930 = [0, 186999603619, 455983659786, 236540988626, 20248800748, 0, 0, 0] := by
  decide +kernel

theorem rows12931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12931 = true := by
  decide +kernel

theorem tot12931 : totK PD2M8K2 D2M8K2.t12931 = [0, 66456686667, 358124871244, 399136740387, 76491582439, 1096156699, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
