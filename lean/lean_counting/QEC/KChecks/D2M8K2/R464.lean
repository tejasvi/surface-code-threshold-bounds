import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1856 = true := by
  decide +kernel

theorem tot1856 : totK PD2M8K2 D2M8K2.t1856 = [0, 0, 237781615395, 500557269233, 145753461912, 2304167554, 0, 0] := by
  decide +kernel

theorem rows1857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1857 = true := by
  decide +kernel

theorem tot1857 : totK PD2M8K2 D2M8K2.t1857 = [0, 0, 177482966799, 456485909568, 227692605589, 15245460789, 0, 0] := by
  decide +kernel

theorem rows1858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1858 = true := by
  decide +kernel

theorem tot1858 : totK PD2M8K2 D2M8K2.t1858 = [0, 0, 195702876249, 488542743550, 202636015050, 9840992866, 0, 0] := by
  decide +kernel

theorem rows1859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1859 = true := by
  decide +kernel

theorem tot1859 : totK PD2M8K2 D2M8K2.t1859 = [0, 0, 198140208344, 482119280058, 182008298485, 6239403452, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
