import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3476 = true := by
  decide +kernel

theorem tot3476 : totK PA10K2 A10K2.t3476 = [0, 0, 83453734878, 832265127811, 1995339825206, 1541698072272, 372930311648, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3477 = true := by
  decide +kernel

theorem tot3477 : totK PA10K2 A10K2.t3477 = [0, 0, 176986670399, 980110404057, 1897845804050, 1420066246455, 249179348749, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3478 = true := by
  decide +kernel

theorem tot3478 : totK PA10K2 A10K2.t3478 = [0, 0, 473182244159, 1695195857448, 1932398296231, 612739892898, 37254374173, 0, 0, 0] := by
  decide +kernel

theorem rows3479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3479 = true := by
  decide +kernel

theorem tot3479 : totK PA10K2 A10K2.t3479 = [0, 0, 110199583916, 1238107839511, 2329895449324, 983958663075, 63299906352, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
