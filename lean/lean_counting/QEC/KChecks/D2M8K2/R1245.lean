import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4980 = true := by
  decide +kernel

theorem tot4980 : totK PD2M8K2 D2M8K2.t4980 = [0, 0, 216004047648, 500708057992, 179170302328, 4866242222, 0, 0] := by
  decide +kernel

theorem rows4981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4981 = true := by
  decide +kernel

theorem tot4981 : totK PD2M8K2 D2M8K2.t4981 = [0, 0, 164928790658, 447208468845, 282749402028, 28985488227, 0, 0] := by
  decide +kernel

theorem rows4982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4982 = true := by
  decide +kernel

theorem tot4982 : totK PD2M8K2 D2M8K2.t4982 = [0, 0, 189630813053, 456598853507, 247022512899, 17399950486, 0, 0] := by
  decide +kernel

theorem rows4983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4983 = true := by
  decide +kernel

theorem tot4983 : totK PD2M8K2 D2M8K2.t4983 = [0, 0, 160057721469, 471825354899, 271891707341, 24125055247, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
