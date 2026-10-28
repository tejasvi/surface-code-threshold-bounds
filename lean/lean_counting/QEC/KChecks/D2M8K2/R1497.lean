import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5988 = true := by
  decide +kernel

theorem tot5988 : totK PD2M8K2 D2M8K2.t5988 = [0, 0, 166911478610, 439055868330, 271047108488, 28460070216, 0, 0] := by
  decide +kernel

theorem rows5989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5989 = true := by
  decide +kernel

theorem tot5989 : totK PD2M8K2 D2M8K2.t5989 = [0, 0, 142132585335, 453669646277, 269827208990, 9144939981, 0, 0] := by
  decide +kernel

theorem rows5990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5990 = true := by
  decide +kernel

theorem tot5990 : totK PD2M8K2 D2M8K2.t5990 = [0, 0, 0, 327774188555, 510139843919, 67784611157, 0, 0] := by
  decide +kernel

theorem rows5991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5991 = true := by
  decide +kernel

theorem tot5991 : totK PD2M8K2 D2M8K2.t5991 = [0, 0, 155931650124, 388430895873, 294453844473, 70451530393, 1392055030, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
