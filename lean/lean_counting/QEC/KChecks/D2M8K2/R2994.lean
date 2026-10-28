import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11976 = true := by
  decide +kernel

theorem tot11976 : totK PD2M8K2 D2M8K2.t11976 = [94864624234, 413120087196, 358592266127, 52092624208, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11977 = true := by
  decide +kernel

theorem tot11977 : totK PD2M8K2 D2M8K2.t11977 = [0, 167659467297, 445835783870, 259431049304, 25358898171, 0, 0, 0] := by
  decide +kernel

theorem rows11978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11978 = true := by
  decide +kernel

theorem tot11978 : totK PD2M8K2 D2M8K2.t11978 = [18232310914, 171361920765, 447006444406, 246624430512, 12058116921, 0, 0, 0] := by
  decide +kernel

theorem rows11979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11979 = true := by
  decide +kernel

theorem tot11979 : totK PD2M8K2 D2M8K2.t11979 = [184355889490, 462787864961, 247070321410, 23086386237, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
