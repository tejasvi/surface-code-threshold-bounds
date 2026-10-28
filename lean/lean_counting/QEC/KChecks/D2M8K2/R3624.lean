import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14496 = true := by
  decide +kernel

theorem tot14496 : totK PD2M8K2 D2M8K2.t14496 = [171898575652, 477998669710, 228142000930, 10853623459, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14497 = true := by
  decide +kernel

theorem tot14497 : totK PD2M8K2 D2M8K2.t14497 = [169412605754, 450973955885, 244961179516, 15218567795, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14498 = true := by
  decide +kernel

theorem tot14498 : totK PD2M8K2 D2M8K2.t14498 = [0, 270582051792, 500060235496, 115469599246, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14499 = true := by
  decide +kernel

theorem tot14499 : totK PD2M8K2 D2M8K2.t14499 = [93305483181, 375992870107, 398639678767, 49815678723, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
