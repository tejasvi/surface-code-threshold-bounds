import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t592 = true := by
  decide +kernel

theorem tot592 : totK PA10K2 A10K2.t592 = [0, 319364639558, 992970468495, 1083894457185, 1194146714918, 889117660028, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

theorem rows593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t593 = true := by
  decide +kernel

theorem tot593 : totK PA10K2 A10K2.t593 = [0, 538351562260, 1937270209057, 1918804123712, 431967114073, 11765040145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t594 = true := by
  decide +kernel

theorem tot594 : totK PA10K2 A10K2.t594 = [0, 0, 651058154065, 2063765477221, 1733741143044, 396048147563, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t595 = true := by
  decide +kernel

theorem tot595 : totK PA10K2 A10K2.t595 = [0, 292130592925, 1208581379906, 1881081951288, 1202597237038, 191820686919, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
