import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4140 = true := by
  decide +kernel

theorem tot4140 : totK PA10K2 A10K2.t4140 = [0, 439258386727, 1790243954568, 2012444008781, 567422869565, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4141 = true := by
  decide +kernel

theorem tot4141 : totK PA10K2 A10K2.t4141 = [0, 104883254851, 919050958860, 2007789439963, 1484233181694, 363409396738, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4142 = true := by
  decide +kernel

theorem tot4142 : totK PA10K2 A10K2.t4142 = [0, 201767328808, 1033572395604, 1976587226849, 1341601292468, 215971790483, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4143 = true := by
  decide +kernel

theorem tot4143 : totK PA10K2 A10K2.t4143 = [0, 267572628447, 1425427765035, 2127845807454, 826694068139, 64746264998, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
