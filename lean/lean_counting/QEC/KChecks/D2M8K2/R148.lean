import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t592 = true := by
  decide +kernel

theorem tot592 : totK PD2M8K2 D2M8K2.t592 = [166335747148, 460994267663, 255886955811, 16575597361, 0, 0, 0, 0] := by
  decide +kernel

theorem rows593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t593 = true := by
  decide +kernel

theorem tot593 : totK PD2M8K2 D2M8K2.t593 = [0, 204531891167, 484916043178, 179064375974, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t594 = true := by
  decide +kernel

theorem tot594 : totK PD2M8K2 D2M8K2.t594 = [87718631415, 341755551032, 363273333113, 93333936897, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t595 = true := by
  decide +kernel

theorem tot595 : totK PD2M8K2 D2M8K2.t595 = [179332268821, 441412412730, 266647714535, 26952216198, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
