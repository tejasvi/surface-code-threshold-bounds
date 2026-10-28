import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12992 = true := by
  decide +kernel

theorem tot12992 : totK PD2M8K2 D2M8K2.t12992 = [0, 0, 314071438965, 506740359751, 73122764551, 0, 0, 0] := by
  decide +kernel

theorem rows12993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12993 = true := by
  decide +kernel

theorem tot12993 : totK PD2M8K2 D2M8K2.t12993 = [0, 180520054459, 443379802295, 270122633793, 32040641828, 0, 0, 0] := by
  decide +kernel

theorem rows12994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12994 = true := by
  decide +kernel

theorem tot12994 : totK PD2M8K2 D2M8K2.t12994 = [0, 188090036206, 469910131258, 239314501900, 14823665076, 0, 0, 0] := by
  decide +kernel

theorem rows12995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12995 = true := by
  decide +kernel

theorem tot12995 : totK PD2M8K2 D2M8K2.t12995 = [0, 49717183811, 284995310144, 373374244304, 174772380055, 21156593246, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
