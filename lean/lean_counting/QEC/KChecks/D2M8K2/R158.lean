import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t632 = true := by
  decide +kernel

theorem tot632 : totK PD2M8K2 D2M8K2.t632 = [195416951428, 463385609743, 248176636452, 23249966035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t633 = true := by
  decide +kernel

theorem tot633 : totK PD2M8K2 D2M8K2.t633 = [183428052861, 478233949588, 231556275382, 14194480791, 0, 0, 0, 0] := by
  decide +kernel

theorem rows634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t634 = true := by
  decide +kernel

theorem tot634 : totK PD2M8K2 D2M8K2.t634 = [0, 287973511805, 501415387657, 116048253690, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t635 = true := by
  decide +kernel

theorem tot635 : totK PD2M8K2 D2M8K2.t635 = [0, 185830059928, 481354795038, 205095167540, 8634438441, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
