import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13772 = true := by
  decide +kernel

theorem tot13772 : totK PD2M8K2 D2M8K2.t13772 = [0, 175061879071, 445521900742, 273605131100, 25812134632, 0, 0, 0] := by
  decide +kernel

theorem rows13773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13773 = true := by
  decide +kernel

theorem tot13773 : totK PD2M8K2 D2M8K2.t13773 = [0, 93773531552, 428596442132, 361822304536, 29811075482, 0, 0, 0] := by
  decide +kernel

theorem rows13774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13774 = true := by
  decide +kernel

theorem tot13774 : totK PD2M8K2 D2M8K2.t13774 = [0, 0, 207804738125, 496631282565, 172432272387, 4882834716, 0, 0] := by
  decide +kernel

theorem rows13775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13775 = true := by
  decide +kernel

theorem tot13775 : totK PD2M8K2 D2M8K2.t13775 = [49567372496, 69446598421, 159904948209, 393397684855, 206650551920, 17014456371, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
