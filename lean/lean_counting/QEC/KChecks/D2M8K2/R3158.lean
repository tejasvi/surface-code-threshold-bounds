import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12632 = true := by
  decide +kernel

theorem tot12632 : totK PD2M8K2 D2M8K2.t12632 = [0, 0, 182420260415, 462199334018, 222259678795, 12373752831, 0, 0] := by
  decide +kernel

theorem rows12633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12633 = true := by
  decide +kernel

theorem tot12633 : totK PD2M8K2 D2M8K2.t12633 = [0, 0, 38511951413, 331550409472, 424533583398, 77023703495, 1164319620, 0] := by
  decide +kernel

theorem rows12634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12634 = true := by
  decide +kernel

theorem tot12634 : totK PD2M8K2 D2M8K2.t12634 = [0, 0, 0, 205876165649, 452182422117, 162806890286, 11727338389, 0] := by
  decide +kernel

theorem rows12635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12635 = true := by
  decide +kernel

theorem tot12635 : totK PD2M8K2 D2M8K2.t12635 = [0, 0, 221376211258, 469525414023, 204781429792, 11027195559, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
