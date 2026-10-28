import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6864 = true := by
  decide +kernel

theorem tot6864 : totK PD2M8K2 D2M8K2.t6864 = [0, 270909005527, 501861912704, 109010427866, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6865 = true := by
  decide +kernel

theorem tot6865 : totK PD2M8K2 D2M8K2.t6865 = [138002238038, 403252189379, 348695922185, 45023278809, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6866 = true := by
  decide +kernel

theorem tot6866 : totK PD2M8K2 D2M8K2.t6866 = [177564893059, 455504142266, 234331780105, 15913366317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6867 = true := by
  decide +kernel

theorem tot6867 : totK PD2M8K2 D2M8K2.t6867 = [105284739419, 426361371758, 352611485961, 47014230131, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
