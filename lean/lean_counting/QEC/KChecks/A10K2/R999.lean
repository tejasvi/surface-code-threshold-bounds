import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3996 = true := by
  decide +kernel

theorem tot3996 : totK PA10K2 A10K2.t3996 = [0, 0, 0, 449442060337, 1876421147100, 2134286585842, 583087212534, 18776452511, 0, 0] := by
  decide +kernel

theorem rows3997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3997 = true := by
  decide +kernel

theorem tot3997 : totK PA10K2 A10K2.t3997 = [0, 480657707117, 1746481795039, 1775343505933, 452755105193, 119653490327, 170531207492, 37324211964, 0, 0] := by
  decide +kernel

theorem rows3998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3998 = true := by
  decide +kernel

theorem tot3998 : totK PA10K2 A10K2.t3998 = [0, 297251734964, 1399014757267, 2163362750901, 1080727683431, 96448336227, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3999 = true := by
  decide +kernel

theorem tot3999 : totK PA10K2 A10K2.t3999 = [0, 109832843262, 739366577484, 1880727415330, 1672987582862, 412850691014, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
