import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6156 = true := by
  decide +kernel

theorem tot6156 : totK PD2M8K2 D2M8K2.t6156 = [194946287859, 487510368009, 219796077412, 10535239315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6157 = true := by
  decide +kernel

theorem tot6157 : totK PD2M8K2 D2M8K2.t6157 = [0, 251641493067, 448382709351, 195404008997, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows6158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6158 = true := by
  decide +kernel

theorem tot6158 : totK PD2M8K2 D2M8K2.t6158 = [0, 189546162305, 491870585517, 208963354970, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows6159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6159 = true := by
  decide +kernel

theorem tot6159 : totK PD2M8K2 D2M8K2.t6159 = [90988959560, 279822414916, 356609208944, 165201523670, 8214505460, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
