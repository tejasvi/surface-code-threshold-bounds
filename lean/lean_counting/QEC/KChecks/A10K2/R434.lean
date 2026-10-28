import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1736 = true := by
  decide +kernel

theorem tot1736 : totK PA10K2 A10K2.t1736 = [0, 0, 287452481429, 1258886895619, 2012113314291, 1202535503815, 200336835985, 5459593153, 0, 0] := by
  decide +kernel

theorem rows1737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1737 = true := by
  decide +kernel

theorem tot1737 : totK PA10K2 A10K2.t1737 = [0, 0, 509805898549, 1906487155308, 2135678370715, 620392128439, 21686146425, 0, 0, 0] := by
  decide +kernel

theorem rows1738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1738 = true := by
  decide +kernel

theorem tot1738 : totK PA10K2 A10K2.t1738 = [0, 0, 0, 725138665017, 2229866012635, 1824211267095, 332451259525, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1739 = true := by
  decide +kernel

theorem tot1739 : totK PA10K2 A10K2.t1739 = [0, 0, 0, 458843250082, 1793240817784, 2032704294469, 660277513357, 49836814157, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
