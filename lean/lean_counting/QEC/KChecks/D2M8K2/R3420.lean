import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13680 = true := by
  decide +kernel

theorem tot13680 : totK PD2M8K2 D2M8K2.t13680 = [0, 186757499667, 462111934203, 222946913940, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows13681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13681 = true := by
  decide +kernel

theorem tot13681 : totK PD2M8K2 D2M8K2.t13681 = [0, 52161743068, 327144249864, 426883925912, 84394904059, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13682 = true := by
  decide +kernel

theorem tot13682 : totK PD2M8K2 D2M8K2.t13682 = [0, 0, 192976675161, 467763673155, 175066762376, 11894306413, 0, 0] := by
  decide +kernel

theorem rows13683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13683 = true := by
  decide +kernel

theorem tot13683 : totK PD2M8K2 D2M8K2.t13683 = [0, 155702246731, 429335371074, 276570760024, 26288110301, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
