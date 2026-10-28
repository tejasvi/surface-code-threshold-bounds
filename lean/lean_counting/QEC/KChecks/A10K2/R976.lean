import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3904 = true := by
  decide +kernel

theorem tot3904 : totK PA10K2 A10K2.t3904 = [0, 0, 0, 632340450170, 2054271617497, 1723261194115, 395828342093, 25371180993, 0, 0] := by
  decide +kernel

theorem rows3905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3905 = true := by
  decide +kernel

theorem tot3905 : totK PA10K2 A10K2.t3905 = [0, 0, 291919316456, 1248709850001, 1886224804567, 1128127478209, 189317554510, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3906 = true := by
  decide +kernel

theorem tot3906 : totK PA10K2 A10K2.t3906 = [0, 0, 268561015556, 1455654335551, 2186128024370, 813142785926, 58834240596, 0, 0, 0] := by
  decide +kernel

theorem rows3907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3907 = true := by
  decide +kernel

theorem tot3907 : totK PA10K2 A10K2.t3907 = [0, 0, 295806202328, 1237898928855, 1921624882476, 1101775612272, 174572958231, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
