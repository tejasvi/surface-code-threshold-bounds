import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7668 = true := by
  decide +kernel

theorem tot7668 : totK PA10K2 A10K2.t7668 = [0, 0, 0, 510015090104, 1862484990369, 2031842185295, 717048393319, 57187409993, 0, 0] := by
  decide +kernel

theorem rows7669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7669 = true := by
  decide +kernel

theorem tot7669 : totK PA10K2 A10K2.t7669 = [0, 0, 0, 312057137912, 1551397052373, 2171555893366, 950054572466, 96363744419, 0, 0] := by
  decide +kernel

theorem rows7670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7670 = true := by
  decide +kernel

theorem tot7670 : totK PA10K2 A10K2.t7670 = [0, 0, 0, 501013369758, 1798991798161, 1954215780275, 601273056934, 31947994545, 0, 0] := by
  decide +kernel

theorem rows7671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7671 = true := by
  decide +kernel

theorem tot7671 : totK PA10K2 A10K2.t7671 = [0, 0, 0, 0, 806472902819, 2249236272053, 1606283722027, 268818979216, 7047025452, 0] := by
  decide +kernel

end QECKChecks.A10K2
