import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14720 = true := by
  decide +kernel

theorem tot14720 : totK PD2M8K2 D2M8K2.t14720 = [0, 85882703395, 347086781219, 393147761554, 78529735548, 1164319620, 0, 0] := by
  decide +kernel

theorem rows14721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14721 = true := by
  decide +kernel

theorem tot14721 : totK PD2M8K2 D2M8K2.t14721 = [0, 50240578857, 293587070677, 441387033955, 118020889867, 4008488258, 0, 0] := by
  decide +kernel

theorem rows14722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14722 = true := by
  decide +kernel

theorem tot14722 : totK PD2M8K2 D2M8K2.t14722 = [0, 178697019320, 462280195532, 252052866619, 22776889198, 0, 0, 0] := by
  decide +kernel

theorem rows14723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14723 = true := by
  decide +kernel

theorem tot14723 : totK PD2M8K2 D2M8K2.t14723 = [0, 193110110305, 476918195428, 218111945624, 12361366339, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
