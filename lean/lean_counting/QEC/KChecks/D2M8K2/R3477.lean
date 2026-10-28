import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13908 = true := by
  decide +kernel

theorem tot13908 : totK PD2M8K2 D2M8K2.t13908 = [0, 216471168222, 482595249871, 196910788628, 7833113735, 0, 0, 0] := by
  decide +kernel

theorem rows13909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13909 = true := by
  decide +kernel

theorem tot13909 : totK PD2M8K2 D2M8K2.t13909 = [0, 181549052496, 457077489365, 252115837689, 18333014298, 0, 0, 0] := by
  decide +kernel

theorem rows13910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13910 = true := by
  decide +kernel

theorem tot13910 : totK PD2M8K2 D2M8K2.t13910 = [0, 159162792406, 486385412819, 235567611751, 8959913991, 0, 0, 0] := by
  decide +kernel

theorem rows13911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13911 = true := by
  decide +kernel

theorem tot13911 : totK PD2M8K2 D2M8K2.t13911 = [0, 175407097617, 448061173328, 245696909690, 22828318141, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
