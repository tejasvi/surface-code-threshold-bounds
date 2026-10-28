import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7056 = true := by
  decide +kernel

theorem tot7056 : totK PA10K2 A10K2.t7056 = [0, 0, 0, 556408274289, 1940482320807, 1822686277789, 387877492524, 12496645144, 0, 0] := by
  decide +kernel

theorem rows7057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7057 = true := by
  decide +kernel

theorem tot7057 : totK PA10K2 A10K2.t7057 = [0, 0, 0, 115970069659, 1033075337890, 2213358720882, 1301393213137, 199528673010, 6725424603, 0] := by
  decide +kernel

theorem rows7058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7058 = true := by
  decide +kernel

theorem tot7058 : totK PA10K2 A10K2.t7058 = [0, 0, 0, 494703685817, 1843987120852, 1838951911050, 522884743581, 31452125142, 0, 0] := by
  decide +kernel

theorem rows7059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7059 = true := by
  decide +kernel

theorem tot7059 : totK PA10K2 A10K2.t7059 = [0, 0, 0, 553324704958, 1982469887206, 1992313552495, 465810548332, 18066489345, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
