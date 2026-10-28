import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8172 = true := by
  decide +kernel

theorem tot8172 : totK PA10K2 A10K2.t8172 = [0, 0, 0, 0, 110843018184, 988619940253, 2126153764822, 1330651356488, 229168410112, 6860445330] := by
  decide +kernel

theorem rows8173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8173 = true := by
  decide +kernel

theorem tot8173 : totK PA10K2 A10K2.t8173 = [0, 0, 0, 0, 829373495225, 2277654141566, 1652594540558, 272829735072, 6315661314, 0] := by
  decide +kernel

theorem rows8174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8174 = true := by
  decide +kernel

theorem tot8174 : totK PA10K2 A10K2.t8174 = [0, 0, 0, 113839911969, 550891224288, 1502743721135, 1971995520902, 777780927200, 62331537917, 0] := by
  decide +kernel

theorem rows8175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8175 = true := by
  decide +kernel

theorem tot8175 : totK PA10K2 A10K2.t8175 = [0, 0, 0, 597481984277, 1974663809419, 1770291044171, 389204144695, 17563258493, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
