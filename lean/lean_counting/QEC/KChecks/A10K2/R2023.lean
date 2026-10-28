import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8092 = true := by
  decide +kernel

theorem tot8092 : totK PA10K2 A10K2.t8092 = [0, 0, 0, 0, 539232185216, 1874671576955, 1909062027951, 550549399748, 34099770725, 0] := by
  decide +kernel

theorem rows8093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8093 = true := by
  decide +kernel

theorem tot8093 : totK PA10K2 A10K2.t8093 = [0, 0, 0, 0, 601588076742, 2013323097313, 1831196925943, 400647870007, 13604820459, 0] := by
  decide +kernel

theorem rows8094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8094 = true := by
  decide +kernel

theorem tot8094 : totK PA10K2 A10K2.t8094 = [0, 0, 0, 0, 0, 956958720772, 2293118829363, 1388600747139, 208912525272, 7380853412] := by
  decide +kernel

theorem rows8095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8095 = true := by
  decide +kernel

theorem tot8095 : totK PA10K2 A10K2.t8095 = [0, 0, 0, 0, 693003297685, 2013832891124, 1642315529376, 425062544691, 32148381784, 0] := by
  decide +kernel

end QECKChecks.A10K2
