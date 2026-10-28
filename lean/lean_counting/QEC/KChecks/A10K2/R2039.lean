import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8156 = true := by
  decide +kernel

theorem tot8156 : totK PA10K2 A10K2.t8156 = [0, 0, 0, 537680587155, 1936746219476, 2061557893669, 574838698498, 18588350288, 0, 0] := by
  decide +kernel

theorem rows8157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8157 = true := by
  decide +kernel

theorem tot8157 : totK PA10K2 A10K2.t8157 = [0, 0, 0, 0, 680220421073, 2177402392080, 1843467142693, 326376249812, 6853348008, 0] := by
  decide +kernel

theorem rows8158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8158 = true := by
  decide +kernel

theorem tot8158 : totK PA10K2 A10K2.t8158 = [0, 0, 0, 0, 519859749494, 1773436909629, 1975810841974, 687755858884, 55498468803, 0] := by
  decide +kernel

theorem rows8159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8159 = true := by
  decide +kernel

theorem tot8159 : totK PA10K2 A10K2.t8159 = [0, 0, 0, 0, 603525227809, 2054064308842, 1815511358941, 331218082947, 12496645144, 0] := by
  decide +kernel

end QECKChecks.A10K2
