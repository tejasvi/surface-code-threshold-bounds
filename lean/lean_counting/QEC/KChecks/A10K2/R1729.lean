import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6916 = true := by
  decide +kernel

theorem tot6916 : totK PA10K2 A10K2.t6916 = [0, 0, 582481005154, 1763306378418, 1710035191192, 614204532296, 66162645450, 0, 0, 0] := by
  decide +kernel

theorem rows6917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6917 = true := by
  decide +kernel

theorem tot6917 : totK PA10K2 A10K2.t6917 = [0, 0, 0, 920560672179, 2278224191059, 1210415709951, 118870150564, 0, 0, 0] := by
  decide +kernel

theorem rows6918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6918 = true := by
  decide +kernel

theorem tot6918 : totK PA10K2 A10K2.t6918 = [0, 0, 488352769765, 1787952583258, 1922401165571, 680422919419, 113565509687, 5705019915, 0, 0] := by
  decide +kernel

theorem rows6919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6919 = true := by
  decide +kernel

theorem tot6919 : totK PA10K2 A10K2.t6919 = [0, 0, 314008318368, 1449214905580, 2151777707751, 1014579489883, 86078930166, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
