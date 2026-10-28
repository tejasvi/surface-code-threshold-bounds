import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1368 = true := by
  decide +kernel

theorem tot1368 : totK PD2M8K2 D2M8K2.t1368 = [0, 184637532865, 442598696583, 250383485853, 25293373355, 0, 0, 0] := by
  decide +kernel

theorem rows1369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1369 = true := by
  decide +kernel

theorem tot1369 : totK PD2M8K2 D2M8K2.t1369 = [0, 129661128079, 447327101363, 310933021412, 24449167834, 0, 0, 0] := by
  decide +kernel

theorem rows1370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1370 = true := by
  decide +kernel

theorem tot1370 : totK PD2M8K2 D2M8K2.t1370 = [0, 0, 209064571161, 488910331091, 171442080711, 4901932702, 0, 0] := by
  decide +kernel

theorem rows1371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1371 = true := by
  decide +kernel

theorem tot1371 : totK PD2M8K2 D2M8K2.t1371 = [0, 0, 187676035823, 466102837097, 215610623260, 17014456371, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
