import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2748 = true := by
  decide +kernel

theorem tot2748 : totK PD2M8K2 D2M8K2.t2748 = [0, 0, 217773060332, 488863841358, 153864443037, 2338671889, 0, 0] := by
  decide +kernel

theorem rows2749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2749 = true := by
  decide +kernel

theorem tot2749 : totK PD2M8K2 D2M8K2.t2749 = [0, 0, 180653325279, 464733691611, 241652946128, 23012758625, 0, 0] := by
  decide +kernel

theorem rows2750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2750 = true := by
  decide +kernel

theorem tot2750 : totK PD2M8K2 D2M8K2.t2750 = [0, 0, 175895175283, 481757840520, 225107911225, 13087943218, 0, 0] := by
  decide +kernel

theorem rows2751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2751 = true := by
  decide +kernel

theorem tot2751 : totK PD2M8K2 D2M8K2.t2751 = [0, 0, 168677618006, 460846040909, 229687826525, 10637642438, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
