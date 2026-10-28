import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1728 = true := by
  decide +kernel

theorem tot1728 : totK PD2M8K2 D2M8K2.t1728 = [0, 0, 26505278472, 332783727753, 477359153577, 61792119735, 0, 0] := by
  decide +kernel

theorem rows1729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1729 = true := by
  decide +kernel

theorem tot1729 : totK PD2M8K2 D2M8K2.t1729 = [0, 0, 198113696899, 471805457741, 223558243445, 12836124098, 0, 0] := by
  decide +kernel

theorem rows1730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1730 = true := by
  decide +kernel

theorem tot1730 : totK PD2M8K2 D2M8K2.t1730 = [0, 0, 188696534307, 482918301456, 219118732305, 13186692860, 0, 0] := by
  decide +kernel

theorem rows1731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1731 = true := by
  decide +kernel

theorem tot1731 : totK PD2M8K2 D2M8K2.t1731 = [0, 0, 177390075719, 476393519146, 254715098451, 11643576422, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
