import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2164 = true := by
  decide +kernel

theorem tot2164 : totK PA10K2 A10K2.t2164 = [0, 0, 659732358654, 2113315809780, 1605451809196, 317738394950, 24969229125, 0, 0, 0] := by
  decide +kernel

theorem rows2165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2165 = true := by
  decide +kernel

theorem tot2165 : totK PA10K2 A10K2.t2165 = [0, 346241136035, 1198323630586, 1733610456740, 1093268018822, 189431769107, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2166 = true := by
  decide +kernel

theorem tot2166 : totK PA10K2 A10K2.t2166 = [0, 474251286325, 1882645747589, 1909267603996, 466369858920, 26386655430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2167 = true := by
  decide +kernel

theorem tot2167 : totK PA10K2 A10K2.t2167 = [0, 0, 875892673163, 2346695129547, 1239242768399, 112069967990, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
