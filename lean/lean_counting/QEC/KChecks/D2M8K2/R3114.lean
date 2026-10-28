import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12456 = true := by
  decide +kernel

theorem tot12456 : totK PD2M8K2 D2M8K2.t12456 = [0, 0, 92057834958, 417655402422, 330656484451, 31495973056, 0, 0] := by
  decide +kernel

theorem rows12457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12457 = true := by
  decide +kernel

theorem tot12457 : totK PD2M8K2 D2M8K2.t12457 = [0, 0, 170627828394, 459987473464, 233874994865, 19759852146, 0, 0] := by
  decide +kernel

theorem rows12458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12458 = true := by
  decide +kernel

theorem tot12458 : totK PD2M8K2 D2M8K2.t12458 = [0, 0, 238836510163, 481316786564, 166000645807, 6769157880, 0, 0] := by
  decide +kernel

theorem rows12459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12459 = true := by
  decide +kernel

theorem tot12459 : totK PD2M8K2 D2M8K2.t12459 = [0, 0, 177050626821, 478455531862, 217304522926, 11974190608, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
