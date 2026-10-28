import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14560 = true := by
  decide +kernel

theorem tot14560 : totK PD2M8K2 D2M8K2.t14560 = [90096249691, 198854381449, 206746359481, 287692976138, 99101322038, 3882006667, 0, 0] := by
  decide +kernel

theorem rows14561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14561 = true := by
  decide +kernel

theorem tot14561 : totK PD2M8K2 D2M8K2.t14561 = [175499744272, 458652736095, 243741561591, 16915769617, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14562 = true := by
  decide +kernel

theorem tot14562 : totK PD2M8K2 D2M8K2.t14562 = [139001670435, 439815763745, 285293979485, 24923350920, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14563 = true := by
  decide +kernel

theorem tot14563 : totK PD2M8K2 D2M8K2.t14563 = [0, 265745430912, 501493466241, 113600773940, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
