import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5192 = true := by
  decide +kernel

theorem tot5192 : totK PA10K2 A10K2.t5192 = [0, 189635563139, 705453448981, 1529024542049, 1747772076811, 652171116522, 42599296307, 0, 0, 0] := by
  decide +kernel

theorem rows5193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5193 = true := by
  decide +kernel

theorem tot5193 : totK PA10K2 A10K2.t5193 = [0, 448915046121, 1787993571940, 1998522604714, 561029989659, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5194 = true := by
  decide +kernel

theorem tot5194 : totK PA10K2 A10K2.t5194 = [0, 146078696275, 1012625461011, 1980184860070, 1402933713148, 350232638140, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5195 = true := by
  decide +kernel

theorem tot5195 : totK PA10K2 A10K2.t5195 = [0, 201767328808, 1033821151391, 1925805495531, 1399368764274, 235986169450, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
