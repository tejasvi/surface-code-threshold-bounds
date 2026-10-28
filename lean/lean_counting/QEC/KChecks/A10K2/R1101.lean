import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4404 = true := by
  decide +kernel

theorem tot4404 : totK PA10K2 A10K2.t4404 = [0, 0, 556873687971, 1984693552661, 1831255226411, 446599327586, 26491486257, 0, 0, 0] := by
  decide +kernel

theorem rows4405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4405 = true := by
  decide +kernel

theorem tot4405 : totK PA10K2 A10K2.t4405 = [0, 0, 503569146391, 1748115740761, 1952156676703, 642831667706, 29870872166, 0, 0, 0] := by
  decide +kernel

theorem rows4406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4406 = true := by
  decide +kernel

theorem tot4406 : totK PA10K2 A10K2.t4406 = [0, 0, 462785939474, 1862891201324, 1969875182413, 472396002093, 26086519006, 0, 0, 0] := by
  decide +kernel

theorem rows4407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4407 = true := by
  decide +kernel

theorem tot4407 : totK PA10K2 A10K2.t4407 = [0, 0, 0, 772009825162, 2323968282767, 1424982717459, 146384224161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
