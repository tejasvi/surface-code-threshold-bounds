import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t464 = true := by
  decide +kernel

theorem tot464 : totK PA10K2 A10K2.t464 = [0, 295030643566, 1463873425369, 2216105431387, 951393321763, 81503051372, 0, 0, 0, 0] := by
  decide +kernel

theorem rows465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t465 = true := by
  decide +kernel

theorem tot465 : totK PA10K2 A10K2.t465 = [0, 110568251524, 832539646682, 1988227704473, 1590033725707, 385839824707, 25313348169, 0, 0, 0] := by
  decide +kernel

theorem rows466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t466 = true := by
  decide +kernel

theorem tot466 : totK PA10K2 A10K2.t466 = [0, 563920809561, 1987170612493, 2030229646003, 544560114842, 31931234985, 0, 0, 0, 0] := by
  decide +kernel

theorem rows467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t467 = true := by
  decide +kernel

theorem tot467 : totK PA10K2 A10K2.t467 = [0, 121824269275, 945487733275, 2155180976680, 1575052789123, 289510901392, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
