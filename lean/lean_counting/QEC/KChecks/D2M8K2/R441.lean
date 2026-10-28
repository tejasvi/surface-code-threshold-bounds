import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1764 = true := by
  decide +kernel

theorem tot1764 : totK PD2M8K2 D2M8K2.t1764 = [0, 0, 190361122791, 475413612159, 237679956897, 16556282449, 0, 0] := by
  decide +kernel

theorem rows1765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1765 = true := by
  decide +kernel

theorem tot1765 : totK PD2M8K2 D2M8K2.t1765 = [0, 0, 200837478513, 490314524737, 209803347556, 5938109439, 0, 0] := by
  decide +kernel

theorem rows1766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1766 = true := by
  decide +kernel

theorem tot1766 : totK PD2M8K2 D2M8K2.t1766 = [0, 0, 187639357274, 461729722381, 222494355310, 13551806682, 0, 0] := by
  decide +kernel

theorem rows1767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1767 = true := by
  decide +kernel

theorem tot1767 : totK PD2M8K2 D2M8K2.t1767 = [0, 0, 0, 313143407334, 487109095941, 88777057820, 1129969115, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
