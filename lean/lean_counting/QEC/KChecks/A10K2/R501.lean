import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2004 = true := by
  decide +kernel

theorem tot2004 : totK PA10K2 A10K2.t2004 = [0, 0, 110544802144, 684599451589, 1874210548390, 1860885021617, 409517378430, 13576218110, 0, 0] := by
  decide +kernel

theorem rows2005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2005 = true := by
  decide +kernel

theorem tot2005 : totK PA10K2 A10K2.t2005 = [0, 0, 373859734312, 1685372417213, 2152188843806, 752073024551, 54493275454, 0, 0, 0] := by
  decide +kernel

theorem rows2006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2006 = true := by
  decide +kernel

theorem tot2006 : totK PA10K2 A10K2.t2006 = [0, 0, 609252834019, 1952414381823, 1875410303836, 549137170774, 30650046427, 0, 0, 0] := by
  decide +kernel

theorem rows2007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2007 = true := by
  decide +kernel

theorem tot2007 : totK PA10K2 A10K2.t2007 = [0, 0, 0, 839006827163, 2323438022157, 1653149921844, 265731824605, 6279851884, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
