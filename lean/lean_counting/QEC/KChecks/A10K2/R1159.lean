import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4636 = true := by
  decide +kernel

theorem tot4636 : totK PA10K2 A10K2.t4636 = [0, 0, 615327380237, 2074891225357, 1819578665135, 394920376383, 12557093595, 0, 0, 0] := by
  decide +kernel

theorem rows4637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4637 = true := by
  decide +kernel

theorem tot4637 : totK PA10K2 A10K2.t4637 = [0, 0, 315863720196, 1577628974487, 2238043416974, 839569350713, 48663178155, 0, 0, 0] := by
  decide +kernel

theorem rows4638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4638 = true := by
  decide +kernel

theorem tot4638 : totK PA10K2 A10K2.t4638 = [0, 592737332747, 1975691015807, 1918750306140, 532136557440, 32243796403, 13968960306, 0, 0, 0] := by
  decide +kernel

theorem rows4639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4639 = true := by
  decide +kernel

theorem tot4639 : totK PA10K2 A10K2.t4639 = [0, 0, 746147232711, 2198827312014, 1702423220364, 348024094792, 11991740650, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
