import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6672 = true := by
  decide +kernel

theorem tot6672 : totK PA10K2 A10K2.t6672 = [165731654200, 1115249064196, 2158238952907, 1360137542924, 243008274591, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6673 = true := by
  decide +kernel

theorem tot6673 : totK PA10K2 A10K2.t6673 = [0, 580129624019, 2045113198310, 1972570155308, 435660801300, 12855574250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6674 = true := by
  decide +kernel

theorem tot6674 : totK PA10K2 A10K2.t6674 = [0, 449161036949, 1653642650066, 1989955863554, 766743765394, 68815120782, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6675 = true := by
  decide +kernel

theorem tot6675 : totK PA10K2 A10K2.t6675 = [0, 343796891401, 1572989411214, 2052946387178, 841738519945, 71115830575, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
