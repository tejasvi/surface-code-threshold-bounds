import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6864 = true := by
  decide +kernel

theorem tot6864 : totK PA10K2 A10K2.t6864 = [0, 0, 442301752188, 1706054808583, 2090243562186, 741651266265, 56060786809, 0, 0, 0] := by
  decide +kernel

theorem rows6865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6865 = true := by
  decide +kernel

theorem tot6865 : totK PA10K2 A10K2.t6865 = [0, 0, 644980769366, 2004058076905, 1783038134294, 388251567814, 11997355697, 0, 0, 0] := by
  decide +kernel

theorem rows6866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6866 = true := by
  decide +kernel

theorem tot6866 : totK PA10K2 A10K2.t6866 = [0, 0, 0, 842745135233, 2311315341737, 1501444835543, 217043516580, 6318667960, 0, 0] := by
  decide +kernel

theorem rows6867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6867 = true := by
  decide +kernel

theorem tot6867 : totK PA10K2 A10K2.t6867 = [0, 0, 366650377627, 1554299908714, 2059703553786, 839232533103, 67827945323, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
