import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7416 = true := by
  decide +kernel

theorem tot7416 : totK PA10K2 A10K2.t7416 = [0, 0, 488652197638, 1814373191684, 2059500404985, 642300469981, 36827966182, 0, 0, 0] := by
  decide +kernel

theorem rows7417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7417 = true := by
  decide +kernel

theorem tot7417 : totK PA10K2 A10K2.t7417 = [0, 0, 226625864075, 1262258567501, 2204514038181, 1214426115454, 137424487451, 0, 0, 0] := by
  decide +kernel

theorem rows7418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7418 = true := by
  decide +kernel

theorem tot7418 : totK PA10K2 A10K2.t7418 = [0, 0, 0, 598382671978, 2053046345758, 1954462081758, 436827268117, 13816090359, 0, 0] := by
  decide +kernel

theorem rows7419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7419 = true := by
  decide +kernel

theorem tot7419 : totK PA10K2 A10K2.t7419 = [0, 0, 0, 401834156581, 1549097513859, 2032526252430, 821541032256, 67674839409, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
