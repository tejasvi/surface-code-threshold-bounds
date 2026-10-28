import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4564 = true := by
  decide +kernel

theorem tot4564 : totK PA10K2 A10K2.t4564 = [0, 526885770501, 1832695010254, 1838762292223, 490647402581, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4565 = true := by
  decide +kernel

theorem tot4565 : totK PA10K2 A10K2.t4565 = [0, 306484836393, 1505461568386, 2094200511832, 707189203087, 51402059204, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4566 = true := by
  decide +kernel

theorem tot4566 : totK PA10K2 A10K2.t4566 = [0, 163944550505, 997014715039, 1980607491207, 1257871574901, 239904770714, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4567 = true := by
  decide +kernel

theorem tot4567 : totK PA10K2 A10K2.t4567 = [0, 462960912405, 1783488778822, 1963178859763, 553945937949, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
