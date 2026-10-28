import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1660 = true := by
  decide +kernel

theorem tot1660 : totK PD2M8K2 D2M8K2.t1660 = [0, 0, 162924183342, 467200351783, 229439724716, 9064506700, 0, 0] := by
  decide +kernel

theorem rows1661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1661 = true := by
  decide +kernel

theorem tot1661 : totK PD2M8K2 D2M8K2.t1661 = [0, 0, 81649623889, 344752371376, 381947136581, 77106474887, 1310285577, 0] := by
  decide +kernel

theorem rows1662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1662 = true := by
  decide +kernel

theorem tot1662 : totK PD2M8K2 D2M8K2.t1662 = [0, 0, 37282526063, 347822717814, 460284161798, 45045281954, 0, 0] := by
  decide +kernel

theorem rows1663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1663 = true := by
  decide +kernel

theorem tot1663 : totK PD2M8K2 D2M8K2.t1663 = [0, 0, 201848678373, 483144772119, 216070639625, 9346569635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
