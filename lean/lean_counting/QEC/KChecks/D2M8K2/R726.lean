import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2904 = true := by
  decide +kernel

theorem tot2904 : totK PD2M8K2 D2M8K2.t2904 = [0, 200160863339, 487206737008, 204927417555, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows2905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2905 = true := by
  decide +kernel

theorem tot2905 : totK PD2M8K2 D2M8K2.t2905 = [90975914836, 286066161103, 337364726570, 166362793980, 8188101860, 0, 0, 0] := by
  decide +kernel

theorem rows2906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2906 = true := by
  decide +kernel

theorem tot2906 : totK PD2M8K2 D2M8K2.t2906 = [168611849833, 444017520844, 274409372829, 30234740898, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2907 = true := by
  decide +kernel

theorem tot2907 : totK PD2M8K2 D2M8K2.t2907 = [160325402645, 460638507279, 269709957990, 17357022955, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
