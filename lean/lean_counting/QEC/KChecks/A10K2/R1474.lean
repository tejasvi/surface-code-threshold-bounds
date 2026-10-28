import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5896 = true := by
  decide +kernel

theorem tot5896 : totK PA10K2 A10K2.t5896 = [0, 0, 0, 0, 698650032508, 2022253749508, 1574864896644, 341994181183, 11740596405, 0] := by
  decide +kernel

theorem rows5897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5897 = true := by
  decide +kernel

theorem tot5897 : totK PA10K2 A10K2.t5897 = [0, 0, 0, 0, 547437932778, 1831290525947, 1710644452652, 477544922285, 31690783744, 0] := by
  decide +kernel

theorem rows5898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5898 = true := by
  decide +kernel

theorem tot5898 : totK PA10K2 A10K2.t5898 = [0, 0, 0, 0, 435580567810, 1665390085751, 1758022376786, 546890427672, 50109395967, 0] := by
  decide +kernel

theorem rows5899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5899 = true := by
  decide +kernel

theorem tot5899 : totK PA10K2 A10K2.t5899 = [0, 0, 0, 0, 301055436795, 1555352687484, 1980874757850, 665278951191, 51971636734, 0] := by
  decide +kernel

end QECKChecks.A10K2
