import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1692 = true := by
  decide +kernel

theorem tot1692 : totK PD2M8K2 D2M8K2.t1692 = [0, 0, 207948562278, 457103197774, 197511811319, 26781561269, 2768613583, 0] := by
  decide +kernel

theorem rows1693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1693 = true := by
  decide +kernel

theorem tot1693 : totK PD2M8K2 D2M8K2.t1693 = [0, 0, 188884265780, 446422702031, 227736241965, 16886077592, 0, 0] := by
  decide +kernel

theorem rows1694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1694 = true := by
  decide +kernel

theorem tot1694 : totK PD2M8K2 D2M8K2.t1694 = [0, 0, 19692840307, 317069903473, 462104838880, 91936796326, 1268739303, 0] := by
  decide +kernel

theorem rows1695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1695 = true := by
  decide +kernel

theorem tot1695 : totK PD2M8K2 D2M8K2.t1695 = [0, 0, 0, 211384732074, 465314262421, 163299569318, 7362961718, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
