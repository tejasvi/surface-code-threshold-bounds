import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7652 = true := by
  decide +kernel

theorem tot7652 : totK PA10K2 A10K2.t7652 = [0, 0, 0, 461429203487, 1914744444566, 1898890658995, 442305989072, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7653 = true := by
  decide +kernel

theorem tot7653 : totK PA10K2 A10K2.t7653 = [0, 0, 452811472891, 1692281531324, 1851421355089, 778460281582, 139702480997, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7654 = true := by
  decide +kernel

theorem tot7654 : totK PA10K2 A10K2.t7654 = [0, 0, 290643499251, 1504179549317, 2088520809347, 745294787720, 54678751475, 0, 0, 0] := by
  decide +kernel

theorem rows7655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7655 = true := by
  decide +kernel

theorem tot7655 : totK PA10K2 A10K2.t7655 = [0, 0, 0, 708906675094, 2190602011822, 1508116890961, 208139160144, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
