import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11708 = true := by
  decide +kernel

theorem tot11708 : totK PD2M8K2 D2M8K2.t11708 = [172114080927, 442452364461, 241340848378, 44777195654, 4431529051, 0, 0, 0] := by
  decide +kernel

theorem rows11709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11709 = true := by
  decide +kernel

theorem tot11709 : totK PD2M8K2 D2M8K2.t11709 = [200478457849, 465038006273, 223554175948, 16809602690, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11710 = true := by
  decide +kernel

theorem tot11710 : totK PD2M8K2 D2M8K2.t11710 = [52876224345, 325253561032, 427411303610, 90835889564, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows11711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11711 = true := by
  decide +kernel

theorem tot11711 : totK PD2M8K2 D2M8K2.t11711 = [0, 204881532250, 472540249273, 185937157354, 11879463720, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
