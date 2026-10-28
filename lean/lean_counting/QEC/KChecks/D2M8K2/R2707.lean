import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10828 = true := by
  decide +kernel

theorem tot10828 : totK PD2M8K2 D2M8K2.t10828 = [0, 0, 181662183390, 456201877114, 268195233751, 27697361298, 0, 0] := by
  decide +kernel

theorem rows10829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10829 = true := by
  decide +kernel

theorem tot10829 : totK PD2M8K2 D2M8K2.t10829 = [0, 0, 166927552458, 458709812376, 257724185401, 17932117704, 0, 0] := by
  decide +kernel

theorem rows10830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10830 = true := by
  decide +kernel

theorem tot10830 : totK PD2M8K2 D2M8K2.t10830 = [0, 0, 0, 278626403136, 484415022555, 127845093964, 4031931762, 0] := by
  decide +kernel

theorem rows10831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10831 = true := by
  decide +kernel

theorem tot10831 : totK PD2M8K2 D2M8K2.t10831 = [0, 0, 89442567638, 337648073449, 397445830114, 90140560013, 1186940923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
