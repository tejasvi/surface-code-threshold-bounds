import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1308 = true := by
  decide +kernel

theorem tot1308 : totK PA10K2 A10K2.t1308 = [0, 304356268031, 1488085887967, 2221167206899, 995102638807, 81562559524, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1309 = true := by
  decide +kernel

theorem tot1309 : totK PA10K2 A10K2.t1309 = [0, 282207666598, 1185614207208, 1884962422126, 1362170055100, 322674740171, 13572172291, 0, 0, 0] := by
  decide +kernel

theorem rows1310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1310 = true := by
  decide +kernel

theorem tot1310 : totK PA10K2 A10K2.t1310 = [0, 506733982092, 1779101568661, 1918210568620, 587098698973, 40681057607, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1311 = true := by
  decide +kernel

theorem tot1311 : totK PA10K2 A10K2.t1311 = [0, 84679404475, 919153788535, 2155698489122, 1601627819674, 292428449849, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
